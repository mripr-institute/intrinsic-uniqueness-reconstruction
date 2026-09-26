import SigmaProbGWCanonical
import Mathlib.MeasureTheory.Function.Floor

namespace Sigma
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology Classical

/-- Natural total size; used only with an explicit almost-sure finiteness proof. -/
def gwNatSize (a : GWOffspringArray) : ℕ := ⌊(gwTotalSize a).toReal⌋₊

theorem gw_nat_size_measurable : Measurable gwNatSize :=
  gw_total_size_measurable.ennreal_toReal.nat_floor

theorem gw_nat_size_cast_of_finite {a : GWOffspringArray} (h : gwTotalSize a < ∞) :
    (gwNatSize a : ℝ≥0∞) = gwTotalSize a := by
  obtain ⟨d, hd⟩ := (gw_total_size_finite_iff_extinct a).mp h
  simp [gwNatSize, gw_total_size_of_extinct hd]

theorem gw_child_total_le {a : GWOffspringArray} {i : ℕ} (hi : i < a []) :
    gwTotalSize (gwChildArray i a) ≤ gwTotalSize a := by
  rw [gw_total_size_root_decomposition a]
  calc
    gwTotalSize (gwChildArray i a) ≤ ∑ j ∈ Finset.range (a []),
        gwTotalSize (gwChildArray j a) :=
      Finset.single_le_sum (f := fun j => gwTotalSize (gwChildArray j a))
        (fun _ _ => zero_le _) (Finset.mem_range.mpr hi)
    _ ≤ 1 + ∑ j ∈ Finset.range (a []), gwTotalSize (gwChildArray j a) := le_add_left le_rfl

theorem gw_nat_size_root_decomposition {a : GWOffspringArray} (h : gwTotalSize a < ∞) :
    gwNatSize a = 1 + ∑ i ∈ Finset.range (a []), gwNatSize (gwChildArray i a) := by
  have hi (i : ℕ) (hi : i ∈ Finset.range (a [])) : gwTotalSize (gwChildArray i a) < ∞ :=
    lt_of_le_of_lt (gw_child_total_le (Finset.mem_range.mp hi)) h
  have he := gw_total_size_root_decomposition a
  rw [← gw_nat_size_cast_of_finite h] at he
  have hsum : (∑ i ∈ Finset.range (a []), gwTotalSize (gwChildArray i a)) =
      ∑ i ∈ Finset.range (a []), (gwNatSize (gwChildArray i a) : ℝ≥0∞) :=
    Finset.sum_congr rfl fun i hi' => (gw_nat_size_cast_of_finite (hi i hi')).symm
  rw [hsum] at he
  exact_mod_cast he

def gwNatSizeLaw (q : PMF ℕ) : Measure ℕ :=
  treeSourceProbability.map (fun ω => gwNatSize (gwOffspring q ω))

instance gwNatSizeLaw_probability (q : PMF ℕ) : IsProbabilityMeasure (gwNatSizeLaw q) :=
  isProbabilityMeasure_map (gw_nat_size_measurable.comp (gw_offspring_measurable q)).aemeasurable

def gwNatSizePMF (q : PMF ℕ) : PMF ℕ := (gwNatSizeLaw q).toPMF

theorem gw_nat_size_pmf_toMeasure (q : PMF ℕ) :
    (gwNatSizePMF q).toMeasure = gwNatSizeLaw q := Measure.toPMF_toMeasure _

theorem gw_nat_size_pgf_lintegral (q : PMF ℕ) (s : ℝ≥0∞) :
    (∫⁻ ω, s ^ gwNatSize (gwOffspring q ω) ∂treeSourceProbability) =
      ∑' n, gwNatSizePMF q n * s^n := by
  have hm : Measurable (fun n : ℕ => s^n) := measurable_of_countable _
  have hmap := lintegral_map (μ := treeSourceProbability) hm
    (show Measurable (fun ω => gwNatSize (gwOffspring q ω)) from
      gw_nat_size_measurable.comp (gw_offspring_measurable q))
  rw [← hmap]
  change (∫⁻ n, s^n ∂gwNatSizeLaw q) = _
  rw [← gw_nat_size_pmf_toMeasure q, lintegral_countable']
  apply tsum_congr
  intro n
  rw [PMF.toMeasure_apply_singleton _ n (measurableSet_singleton n)]
  exact mul_comm _ _

/-- The total-size equation is derived from the actual iid tree whenever its
actual counting-measure size is almost surely finite. -/
theorem gw_nat_size_pgf_conditioning (q : PMF ℕ)
    (hfinite : ∀ᵐ ω ∂treeSourceProbability, gwTotalSize (gwOffspring q ω) < ∞)
    (s : ℝ≥0∞) (hs : s ≤ 1) :
    (∑' n, gwNatSizePMF q n * s^n) =
      s * ∑' n, q n * (∑' k, gwNatSizePMF q k * s^k)^n := by
  let f : TreeSource → ℝ≥0∞ := fun ω => s ^ gwNatSize (gwOffspring q ω)
  have hf : Measurable f := (measurable_of_countable (fun n : ℕ => s^n)).comp
    (gw_nat_size_measurable.comp (gw_offspring_measurable q))
  have he : f =ᵐ[treeSourceProbability] fun ω =>
      s * ∏ i ∈ Finset.range (treeRootOffspring q ω), f (treeChildSource i ω) := by
    filter_upwards [hfinite] with ω hω
    change s ^ gwNatSize (gwOffspring q ω) = _
    rw [gw_nat_size_root_decomposition hω, pow_add, pow_one, ← Finset.prod_pow_eq_pow_sum]
    rfl
  calc
    (∑' n, gwNatSizePMF q n * s^n) = ∫⁻ ω, f ω ∂treeSourceProbability :=
      (gw_nat_size_pgf_lintegral q s).symm
    _ = ∫⁻ ω, s * ∏ i ∈ Finset.range (treeRootOffspring q ω),
        f (treeChildSource i ω) ∂treeSourceProbability := lintegral_congr_ae he
    _ = s * ∫⁻ ω, ∏ i ∈ Finset.range (treeRootOffspring q ω),
        f (treeChildSource i ω) ∂treeSourceProbability :=
      lintegral_const_mul' _ _ (ne_top_of_le_ne_top ENNReal.one_ne_top hs)
    _ = s * ∑' n, q n * (∑' k, gwNatSizePMF q k * s^k)^n := by
      rw [tree_offspring_product_lintegral q f hf]
      change s * ∑' n, q n * (∫⁻ ω, s ^ gwNatSize (gwOffspring q ω) ∂treeSourceProbability)^n = _
      rw [gw_nat_size_pgf_lintegral]

theorem gw_nat_size_pgf_real_conditioning (q : PMF ℕ)
    (hfinite : ∀ᵐ ω ∂treeSourceProbability, gwTotalSize (gwOffspring q ω) < ∞)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    natProbabilityGenerating (gwNatSizePMF q) s =
      s * natProbabilityGenerating q (natProbabilityGenerating (gwNatSizePMF q) s) := by
  have hs : ENNReal.ofReal s ≤ 1 := by
    simpa using ENNReal.ofReal_le_ofReal hs1
  have h := congrArg ENNReal.toReal (gw_nat_size_pgf_conditioning q hfinite (ENNReal.ofReal s) hs)
  rw [ENNReal.toReal_mul,
    nat_probability_generating_ennreal_toReal (gwNatSizePMF q) _ hs,
    nat_probability_generating_ennreal_toReal q _
      (nat_probability_generating_ennreal_le_one (gwNatSizePMF q) _ hs),
    nat_probability_generating_ennreal_toReal (gwNatSizePMF q) _ hs,
    ENNReal.toReal_ofReal hs0] at h
  exact h

end
end Sigma
