import SigmaProbGWExtinction
import SigmaProbGWSize
import SigmaProbGWBorel
import SigmaProbGWLaw

namespace Sigma
noncomputable section
open MeasureTheory Measure Set Filter ProbabilityTheory
open scoped ENNReal

/-- Borel total size as a law on the extended nonnegative reals, so equality of
laws records the absence of infinite trees explicitly. -/
def borelExtendedProbability : Measure ℝ≥0∞ :=
  borelProbability.map (fun n : ℕ => (n : ℝ≥0∞))

def gwTotalSizeLaw (q : PMF ℕ) : Measure ℝ≥0∞ :=
  treeSourceProbability.map (fun ω => gwTotalSize (gwOffspring q ω))

theorem borel_extended_finite_ae :
    ∀ᵐ x ∂borelExtendedProbability, x < ∞ := by
  apply (ae_map_iff (measurable_of_countable (fun n : ℕ => (n : ℝ≥0∞))).aemeasurable
    measurableSet_Iio).mpr
  exact Eventually.of_forall fun n => ENNReal.natCast_lt_top n

theorem gw_total_size_borel_finite_ae (q : PMF ℕ)
    (h : gwTotalSizeLaw q = borelExtendedProbability) :
    ∀ᵐ ω ∂treeSourceProbability, gwTotalSize (gwOffspring q ω) < ∞ := by
  apply (ae_map_iff (gw_total_size_measurable.comp (gw_offspring_measurable q)).aemeasurable
    measurableSet_Iio).mp
  change ∀ᵐ x ∂gwTotalSizeLaw q, x < ∞
  rw [h]
  exact borel_extended_finite_ae

theorem gw_total_size_borel_nat_pmf (q : PMF ℕ)
    (h : gwTotalSizeLaw q = borelExtendedProbability) : gwNatSizePMF q = borelPMF := by
  let f : ℝ≥0∞ → ℕ := fun x => ⌊x.toReal⌋₊
  have hf : Measurable f := measurable_id.ennreal_toReal.nat_floor
  have he := congrArg (fun μ : Measure ℝ≥0∞ => μ.map f) h
  unfold gwTotalSizeLaw borelExtendedProbability at he
  change (treeSourceProbability.map (gwTotalSize ∘ gwOffspring q)).map f =
    (borelProbability.map (fun n : ℕ => (n : ℝ≥0∞))).map f at he
  rw [Measure.map_map hf (gw_total_size_measurable.comp (gw_offspring_measurable q)),
    Measure.map_map hf (measurable_of_countable (fun n : ℕ => (n : ℝ≥0∞)))] at he
  have hi : (f ∘ (fun n : ℕ => (n : ℝ≥0∞))) = id := by
    funext n
    simp [f]
  rw [hi,Measure.map_id] at he
  apply PMF.toMeasure_injective
  rw [gw_nat_size_pmf_toMeasure]
  exact he

theorem gw_total_size_law_of_finite (q : PMF ℕ)
    (hfinite : ∀ᵐ ω ∂treeSourceProbability, gwTotalSize (gwOffspring q ω) < ∞) :
    gwTotalSizeLaw q = (gwNatSizePMF q).toMeasure.map (fun n : ℕ => (n : ℝ≥0∞)) := by
  rw [gw_nat_size_pmf_toMeasure,gwNatSizeLaw]
  change gwTotalSizeLaw q =
    (treeSourceProbability.map (gwNatSize ∘ gwOffspring q)).map (fun n : ℕ => (n : ℝ≥0∞))
  rw [Measure.map_map
    (measurable_of_countable (fun n : ℕ => (n : ℝ≥0∞)))
    (gw_nat_size_measurable.comp (gw_offspring_measurable q))]
  apply Measure.map_congr
  exact hfinite.mono fun ω hω => (gw_nat_size_cast_of_finite hω).symm

theorem gw_poisson_nat_size_borel : gwNatSizePMF (poissonPMF 1) = borelPMF := by
  apply nat_pgf_poisson_branching_identifies_borel
  intro s hs0 hs1
  simpa only [poisson_one_native_pgf] using
    gw_nat_size_pgf_real_conditioning (poissonPMF 1) gw_poisson_total_size_finite_ae s hs0.le hs1.le

/-- Forward direction for the actual iid Poisson tree, including absence of
infinite size mass. -/
theorem gw_poisson_total_size_borel :
    gwTotalSizeLaw (poissonPMF 1) = borelExtendedProbability := by
  rw [gw_total_size_law_of_finite _ gw_poisson_total_size_finite_ae,gw_poisson_nat_size_borel]
  rfl

/-- Exact Borel/Poisson equivalence for the native one-ancestor construction.
The hypothesis is the complete extended total-size law, with no finiteness or
branching-equation assumptions. -/
theorem gw_total_size_borel_iff_poisson (q : PMF ℕ) :
    gwTotalSizeLaw q = borelExtendedProbability ↔ q = poissonPMF 1 := by
  constructor
  · intro h
    have hf := gw_total_size_borel_finite_ae q h
    have hp := gw_total_size_borel_nat_pmf q h
    apply offspring_pgf_equation_identifies_poisson
    intro s hs0 hs1
    simpa only [hp,borel_native_pgf] using
      gw_nat_size_pgf_real_conditioning q hf s hs0.le hs1.le
  · rintro rfl
    exact gw_poisson_total_size_borel

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The same equivalence holds for every supplied native iid offspring array,
on any probability space, in the fixed rooted-tree construction. -/
theorem iid_gw_borel_iff_poisson (q : PMF ℕ) (μ : Measure Ω)
    (X : Ω → GWOffspringArray) (hX : ∀ w, Measurable (fun ω => X ω w))
    (hI : iIndepFun (fun _ : List ℕ => inferInstance) (fun w ω => X ω w) μ)
    (hL : ∀ w, μ.map (fun ω => X ω w) = q.toMeasure) :
    μ.map (fun ω => gwTotalSize (X ω)) = borelExtendedProbability ↔ q = poissonPMF 1 := by
  have h := iid_gw_tree_law_unique q μ treeSourceProbability X (gwOffspring q)
    hX (fun w => (measurable_pi_apply w).comp (gw_offspring_measurable q))
    hI (gw_offspring_independent q) hL (gw_offspring_coordinate_law q)
  rw [h.2]
  exact gw_total_size_borel_iff_poisson q

/-- Observing the Borel total-size law determines the complete random rooted
tree law, within the stipulated iid construction. -/
theorem iid_gw_borel_determines_tree_law (q : PMF ℕ) (μ : Measure Ω)
    (X : Ω → GWOffspringArray) (hX : ∀ w, Measurable (fun ω => X ω w))
    (hI : iIndepFun (fun _ : List ℕ => inferInstance) (fun w ω => X ω w) μ)
    (hL : ∀ w, μ.map (fun ω => X ω w) = q.toMeasure)
    (hB : μ.map (fun ω => gwTotalSize (X ω)) = borelExtendedProbability) :
    μ.map (fun ω => gwTree (X ω)) =
      treeSourceProbability.map (fun ω => gwTree (gwOffspring (poissonPMF 1) ω)) := by
  have hq := (iid_gw_borel_iff_poisson q μ X hX hI hL).mp hB
  subst q
  exact (iid_gw_tree_law_unique (poissonPMF 1) μ treeSourceProbability X
    (gwOffspring (poissonPMF 1)) hX
    (fun w => (measurable_pi_apply w).comp (gw_offspring_measurable _))
    hI (gw_offspring_independent _) hL (gw_offspring_coordinate_law _)).1

end
end Sigma
