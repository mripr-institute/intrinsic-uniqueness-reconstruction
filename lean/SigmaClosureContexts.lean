import SigmaClosure
import SigmaProbGammaProcessExistence
import SigmaOpCanonicalClosure
import SigmaOperatorPearson
import SigmaMatrixGeometry
import SigmaProbGWIdentification
import SigmaRadialSphereGaussian
import SigmaRadialIsotropy

/-!
The five completed native fixed-context clauses of `final:global-E`.
Each candidate predicate records mathematical conditions, not equality to a
recipe. The universal Thom clause is not asserted here.
-/

namespace Sigma.Closure
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators Matrix ComplexOrder

/-- The probability-convolution category, retaining its nonnegative support and
marked starting time. No time regularity is assumed. -/
def ProbabilityConvolutionContext (μ : ℝ≥0 → Measure ℝ) : Prop :=
  (∀ r, IsProbabilityMeasure (μ r)) ∧
  (∀ r, ∀ᵐ t ∂μ r, 0 ≤ t) ∧ μ 0 = Measure.dirac 0 ∧
  (∀ r s, independentAffineSum (μ r) (μ s) 1 = μ (r+s))

theorem gamma_completion_context : ProbabilityConvolutionContext gammaCompletion :=
  ⟨fun _ => inferInstance, gamma_completion_nonnegative, gamma_completion_zero,
    gamma_completion_convolution⟩

/-- The actual time-one observation identifies exactly the canonical family
within the retained probability-convolution category; the reverse observation
is part of the same equivalence. -/
theorem convolution_context_time_one_iff (μ : ℝ≥0 → Measure ℝ)
    (hμ : ProbabilityConvolutionContext μ) :
    μ 1 = gammaProbability ↔ μ = gammaCompletion := by
  constructor
  · exact gamma_completion_unique μ hμ.1 hμ.2.1 hμ.2.2.2
  · rintro rfl
    exact gamma_completion_one

theorem convolution_context_exists_unique :
    ∃! μ : ℝ≥0 → Measure ℝ,
      ProbabilityConvolutionContext μ ∧ μ 1 = gammaProbability := by
  refine ⟨gammaCompletion, ⟨gamma_completion_context, gamma_completion_one⟩, ?_⟩
  intro μ hμ
  exact (convolution_context_time_one_iff μ hμ.1).mp hμ.2

/-- The same completion has an actual global increasing right-continuous
process realization. Its construction is not an input to the fibre theorem. -/
theorem convolution_context_process_realization :
    IsGammaTimeOneProcess poissonClockProbability nativeGammaProcess ∧
    (∀ r, poissonClockProbability.map (nativeGammaProcess r) = gammaCompletion r) ∧
    (∀ᵐ ω ∂poissonClockProbability,
      Monotone (fun r => nativeGammaProcess r ω) ∧
      ∀ r, ContinuousWithinAt (fun s => nativeGammaProcess s ω) (Ici r) r) :=
  ⟨native_gamma_process_category, native_gamma_process_marginal,
    native_gamma_process_paths.mono fun _ h => h.2⟩

/-- The marked differential context retains the literal compact-test operator
on the actual Gamma-weighted Hilbert space and asks for self-adjoint extension. -/
def LaguerreClosureContext
    (T : LaguerreWeightedHilbert →ₗ.[ℂ] LaguerreWeightedHilbert) : Prop :=
  IsSelfAdjoint T ∧ laguerreMinimalOperator ≤ T

theorem laguerre_canonical_context : LaguerreClosureContext laguerreCanonicalOperator := by
  refine ⟨laguerre_canonical_selfAdjoint, ?_⟩
  rw [laguerre_canonical_eq_spectral]
  exact laguerre_minimal_le_spectral

theorem laguerre_context_iff
    (T : LaguerreWeightedHilbert →ₗ.[ℂ] LaguerreWeightedHilbert) :
    LaguerreClosureContext T ↔ T = laguerreCanonicalOperator := by
  constructor
  · intro hT
    exact laguerre_canonical_unique_selfAdjoint_extension T hT.1 hT.2
  · rintro rfl
    exact laguerre_canonical_context

theorem laguerre_context_exists_unique :
    ∃! T : LaguerreWeightedHilbert →ₗ.[ℂ] LaguerreWeightedHilbert,
      LaguerreClosureContext T :=
  ⟨laguerreCanonicalOperator, laguerre_canonical_context,
    fun T hT => (laguerre_context_iff T).mp hT⟩

/-- Retained marked-coordinate data recover the intrinsic density and hence H.
Local AC, mass and the normalized Pearson equation are identifying conditions;
neither the target density nor a stationary-law conclusion is assumed. -/
theorem laguerre_coordinate_intrinsic_reverse (w : ℝ → ℝ)
    (hw : LocallyIntegralAbsolutelyContinuousPositive w)
    (hmass : (∫ t : ℝ in Ioi 0, w t) = 1)
    (hP : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      HasDerivAt (fun s => s*w s) ((2-t)*w t) t) :
    (∀ t > 0, w t = SigmaPresentations.density t) ∧
    (∀ t > 0, 1 + Real.log (w t) = SigmaPresentations.H t) ∧
    volume.withDensity ((Ioi (0 : ℝ)).indicator (fun t => ENNReal.ofReal (w t))) =
      gammaProbability := by
  have he := local_ac_pearson_density_unique w hw hP hmass
  refine ⟨he, ?_, local_ac_pearson_weight_measure w hw hP hmass⟩
  intro t ht
  rw [he t ht]
  exact (intrinsic_log_density ht).symm

theorem laguerre_coordinate_context_exists :
    ∃ w : ℝ → ℝ, LocallyIntegralAbsolutelyContinuousPositive w ∧
      (∀ t > 0, 0 < w t) ∧ (∫ t : ℝ in Ioi 0, w t) = 1 ∧
      (∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
        HasDerivAt (fun s => s*w s) ((2-t)*w t) t) := by
  refine ⟨SigmaPresentations.density, canonical_density_local_integral_ac,
    fun _ ht => SigmaPresentations.density_pos ht, intrinsic_density_integral_one, ?_⟩
  exact ae_of_all _ operator_pearson_flux_derivative

/-- Positive-rank matrix candidates retain their scalar seed, scalar-block
recursion on diagonal matrices, and invariance under every orthogonal basis
change. These sufficient conditions impose no analytic regularity. -/
def MatrixSpectralContext
    (F : (k : ℕ) → Matrix (Fin (k+1)) (Fin (k+1)) ℝ → ℝ) : Prop :=
  (∀ t > 0, F 0 (Matrix.diagonal (fun _ : Fin 1 => t)) = SigmaBase.potential t) ∧
  (∀ k (d : Fin (k+1) → ℝ), (∀ i, 0 < d i) → ∀ t > 0,
    F (k+1) (Matrix.diagonal (Fin.cons t d)) =
      SigmaBase.potential t + F k (Matrix.diagonal d)) ∧
  (∀ k (X : Matrix (Fin (k+1)) (Fin (k+1)) ℝ), X.PosDef →
    ∀ Q : Matrix.unitaryGroup (Fin (k+1)) ℝ,
      F k ((Q : Matrix _ _ _) * X * Star.star (Q : Matrix _ _ _)) = F k X)

theorem matrix_context_diagonal {k : ℕ} (d : Fin k → ℝ) (hd : ∀ i, 0 < d i) :
    matrixPotential (Matrix.diagonal d) = ∑ i, SigmaBase.potential (d i) := by
  simp only [matrixPotential, Matrix.trace_diagonal, Matrix.det_diagonal]
  rw [Real.log_prod Finset.univ _ (fun i _ => ne_of_gt (hd i))]
  simp only [SigmaBase.potential, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one]
  ring

theorem matrix_potential_context : MatrixSpectralContext (fun _ => matrixPotential) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    change matrixPotential (Matrix.diagonal (fun _ : Fin 1 => t)) = SigmaBase.potential t
    rw [matrix_context_diagonal _ (fun _ => ht)]
    simp
  · intro k d hd t ht
    change matrixPotential (Matrix.diagonal (Fin.cons t d)) =
      SigmaBase.potential t + matrixPotential (Matrix.diagonal d)
    have hc : ∀ i : Fin (k+2), (0 : ℝ) < (Fin.cons t d : Fin (k+2) → ℝ) i := by
      intro i
      refine Fin.cases ?_ ?_ i
      · simpa using ht
      · intro j
        simpa using hd j
    rw [matrix_context_diagonal _ hc,
      matrix_context_diagonal _ hd]
    simp [Fin.sum_univ_succ]
  · intro k X hX Q
    exact matrixPotential_orthogonal_congruence X Q (by
      simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
        using unitary.coe_star_mul_self Q)

/-- Equality is asserted exactly on positive-definite matrices, not on arbitrary
off-domain extensions of a candidate family. -/
theorem matrix_context_iff
    (F : (k : ℕ) → Matrix (Fin (k+1)) (Fin (k+1)) ℝ → ℝ) :
    MatrixSpectralContext F ↔
      ∀ k (X : Matrix (Fin (k+1)) (Fin (k+1)) ℝ), X.PosDef → F k X = matrixPotential X := by
  constructor
  · intro hF
    exact spd_positive_rank_lift_unique F hF.1 hF.2.1 hF.2.2
  · intro he
    refine ⟨?_, ?_, ?_⟩
    · intro t ht
      rw [he _ _ (Matrix.PosDef.diagonal (fun _ => ht))]
      exact matrix_potential_context.1 t ht
    · intro k d hd t ht
      rw [he _ _ (Matrix.PosDef.diagonal ((fun i => Fin.cases ht hd i))),
        he _ _ (Matrix.PosDef.diagonal hd)]
      exact matrix_potential_context.2.1 k d hd t ht
    · intro k X hX Q
      have hconj : ((Q : Matrix _ _ _) * X * Star.star (Q : Matrix _ _ _)).PosDef := by
        simpa using positive_definite_congruence X (Star.star (Q : Matrix _ _ _)) hX
          (unitary.toUnits (Star.star Q)).isUnit
      rw [he _ _ hconj, he _ _ hX]
      exact matrix_potential_context.2.2 k X hX Q

theorem matrix_context_rank_one_reverse
    (F : (k : ℕ) → Matrix (Fin (k+1)) (Fin (k+1)) ℝ → ℝ)
    (hF : MatrixSpectralContext F) (t : ℝ) (ht : 0 < t) :
    F 0 (Matrix.diagonal (fun _ : Fin 1 => t)) = SigmaBase.potential t ∧
      -F 0 (Matrix.diagonal (fun _ : Fin 1 => t)) = SigmaPresentations.H t := by
  rw [hF.1 t ht, SigmaPresentations.H_eq_neg_potential]
  exact ⟨rfl,rfl⟩

/-- Literal positive-definite-domain families, avoiding irrelevant off-domain
values when stating unique existence. -/
abbrev PositiveMatrixFamily :=
  (k : ℕ) → {X : Matrix (Fin (k+1)) (Fin (k+1)) ℝ // X.PosDef} → ℝ

def positiveMatrixExtension (F : PositiveMatrixFamily) (k : ℕ)
    (X : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) : ℝ := by
  classical
  exact if h : X.PosDef then F k ⟨X,h⟩ else 0

def PositiveMatrixContext (F : PositiveMatrixFamily) : Prop :=
  MatrixSpectralContext (positiveMatrixExtension F)

theorem matrix_context_exists_unique :
    ∃! F : PositiveMatrixFamily, PositiveMatrixContext F := by
  refine ⟨fun _ X => matrixPotential X.val, ?_, ?_⟩
  · apply (matrix_context_iff _).mpr
    intro k X hX
    simp [positiveMatrixExtension, hX]
  · intro F hF
    funext k X
    have h := (matrix_context_iff _).mp hF k X.val X.property
    simpa [positiveMatrixExtension, X.property] using h

/-- In the actual one-ancestor iid construction the complete extended size law
identifies the offspring law, and the identified law fixes the entire tree. -/
theorem gw_context_identification {Ω : Type*} [MeasurableSpace Ω]
    (q : PMF ℕ) (P : Measure Ω) (X : Ω → GWOffspringArray)
    (hX : ∀ w, Measurable (fun ω => X ω w))
    (hI : iIndepFun (fun _ : List ℕ => inferInstance) (fun w ω => X ω w) P)
    (hL : ∀ w, P.map (fun ω => X ω w) = q.toMeasure) :
    (P.map (fun ω => gwTotalSize (X ω)) = borelExtendedProbability ↔ q = poissonPMF 1) ∧
    (P.map (fun ω => gwTotalSize (X ω)) = borelExtendedProbability →
      P.map (fun ω => gwTree (X ω)) =
        treeSourceProbability.map (fun ω => gwTree (gwOffspring (poissonPMF 1) ω))) :=
  ⟨iid_gw_borel_iff_poisson q P X hX hI hL,
    iid_gw_borel_determines_tree_law q P X hX hI hL⟩

theorem gw_context_exists_unique_offspring :
    ∃! q : PMF ℕ, gwTotalSizeLaw q = borelExtendedProbability :=
  ⟨poissonPMF 1, gw_poisson_total_size_borel,
    fun q hq => (gw_total_size_borel_iff_poisson q).mp hq⟩

theorem gw_context_native_realization :
    Measurable (gwOffspring (poissonPMF 1)) ∧
    iIndepFun (fun _ : List ℕ => inferInstance)
      (fun w ω => gwOffspring (poissonPMF 1) ω w) treeSourceProbability ∧
    (∀ w, treeSourceProbability.map (fun ω => gwOffspring (poissonPMF 1) ω w) =
      (poissonPMF 1).toMeasure) ∧
    gwTotalSizeLaw (poissonPMF 1) = borelExtendedProbability ∧
    HasSum (fun n : ℕ => (n : ℝ) * (poissonPMF 1 n).toReal) 1 :=
  ⟨gw_offspring_measurable _, gw_offspring_independent _, gw_offspring_coordinate_law _,
    gw_poisson_total_size_borel, poisson_mean_hasSum⟩

/-- The marked inverse of the complete Borel PGF recovers the same intrinsic H;
the interval is the fixed branch on which that inverse is identifying. -/
theorem gw_context_intrinsic_reverse (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    borelGenerating (borelInverse t) = t ∧
      Real.log (borelInverse t) = SigmaPresentations.H t := by
  refine ⟨borel_generating_left_inverse t ⟨ht.le,ht1⟩, ?_⟩
  rw [borelInverse, Real.log_mul ht.ne' (Real.exp_ne_zero _), Real.log_exp]
  unfold SigmaPresentations.H
  ring

/-- The supplied Euclidean dimension, energy coordinate and all orthogonal
symmetries are retained; no density or Gaussian law is assumed. -/
def IsotropicFourContext (μ : Measure (EuclideanSpace ℝ (Fin 4))) : Prop :=
  IsProbabilityMeasure μ ∧
    ∀ U : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4), μ.map U = μ

theorem gaussian_radial_context : IsotropicFourContext radialFourGaussian :=
  ⟨inferInstance, radial_four_gaussian_orthogonal⟩

theorem gaussian_radial_context_iff (μ : Measure (EuclideanSpace ℝ (Fin 4)))
    (hμ : IsotropicFourContext μ) :
    μ.map radialFourEnergy = gammaProbability ↔ μ = radialFourGaussian := by
  letI := hμ.1
  exact radial_four_isotropic_energy_iff μ hμ.2

/-- The native Gaussian is the unique candidate with the complete marked
radial-energy observation, within the actual isotropic four-dimensional class. -/
theorem gaussian_radial_context_exists_unique :
    ∃! μ : Measure (EuclideanSpace ℝ (Fin 4)),
      IsotropicFourContext μ ∧ μ.map radialFourEnergy = gammaProbability := by
  refine ⟨radialFourGaussian, ⟨gaussian_radial_context, radial_four_gaussian_energy⟩, ?_⟩
  intro μ hμ
  exact (gaussian_radial_context_iff μ hμ.1).mp hμ.2

/-- The geometric inverse uses an actual independent uniform sphere factor.
The resulting complete radial law carries the intrinsic density and H. -/
theorem gaussian_radial_context_inverse :
    (radialFourUniformSphere.prod gammaProbability).map radialFourUniformLift =
      radialFourGaussian ∧
    (∀ t > 0, SigmaPresentations.H t = 1 + Real.log (SigmaPresentations.density t)) :=
  ⟨radial_four_uniform_gamma_lift, fun _ ht => intrinsic_log_density ht⟩

theorem gaussian_radial_context_intrinsic_reverse
    (μ : Measure (EuclideanSpace ℝ (Fin 4))) (hμ : IsotropicFourContext μ)
    (hE : μ.map radialFourEnergy = gammaProbability) :
    μ = radialFourGaussian ∧
    μ.map radialFourEnergy = volume.withDensity
      ((Ioi (0 : ℝ)).indicator (fun t => ENNReal.ofReal (SigmaPresentations.density t))) ∧
    (∀ t > 0, SigmaPresentations.H t = 1 + Real.log (SigmaPresentations.density t)) := by
  refine ⟨(gaussian_radial_context_iff μ hμ).mp hE, ?_, fun _ ht => intrinsic_log_density ht⟩
  rw [hE]
  exact (local_ac_pearson_weight_measure SigmaPresentations.density
    canonical_density_local_integral_ac (ae_of_all _ operator_pearson_flux_derivative)
    intrinsic_density_integral_one).symm

end
end Sigma.Closure
