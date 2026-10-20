import FailureOfSemipositiveMetricExtension.GlobalBlowdownRationalCoordinates
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! Genuine Zariski basic opens in the prime spectrum of the affine coordinate
ring. Their complex evaluation points recover the exact blow-down complement;
the inverse ratios are actual elements of the corresponding localizations. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.BlowdownComplement
noncomputable section
open Set MvPolynomial TopologicalSpace

/-- A complex affine point as its evaluation prime ideal in the actual spectrum. -/
def evaluationPoint (q : Fin 3 → ℂ) : PrimeSpectrum AffinePolynomial :=
  ⟨RingHom.ker (eval q),RingHom.ker_isPrime (eval q)⟩

@[simp] theorem evaluationPoint_mem_basicOpen (q : Fin 3 → ℂ) (f : AffinePolynomial) :
    evaluationPoint q ∈ PrimeSpectrum.basicOpen f ↔ eval q f ≠ 0 := Iff.rfl

def chartDenominator (a : Fin 3) (e : Fin 4 → Fin 2) : AffinePolynomial :=
  ∏ r, affinePair a r (e r)

theorem chartDenominator_nonzero (a : Fin 3) (e : Fin 4 → Fin 2) : chartDenominator a e ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun r _ => affinePair_ne_zero a r (e r))

/-- The actual principal Zariski open selecting one nonzero component per pair. -/
def zariskiChart (a : Fin 3) (e : Fin 4 → Fin 2) : Opens (PrimeSpectrum AffinePolynomial) :=
  PrimeSpectrum.basicOpen (chartDenominator a e)

theorem zariskiChart_dense (a : Fin 3) (e : Fin 4 → Fin 2) :
    Dense (zariskiChart a e : Set (PrimeSpectrum AffinePolynomial)) := by
  apply (zariskiChart a e).isOpen.dense
  refine ⟨⟨⊥,Ideal.bot_prime⟩,?_⟩
  exact chartDenominator_nonzero a e

@[simp] theorem evaluationPoint_mem_zariskiChart (a : Fin 3) (e : Fin 4 → Fin 2)
    (q : Fin 3 → ℂ) : evaluationPoint q ∈ zariskiChart a e ↔
      ∀ r, eval q (affinePair a r (e r)) ≠ 0 := by
  change eval q (chartDenominator a e) ≠ 0 ↔ _
  simp [chartDenominator,map_prod,Finset.prod_ne_zero_iff]

def zariskiComplement (a : Fin 3) : Opens (PrimeSpectrum AffinePolynomial) :=
  ⨆ e : Fin 4 → Fin 2, zariskiChart a e

/-- The original four-centre complement is exactly the complex-point inverse
image of this actual Zariski open in every affine plane chart. -/
theorem baseAway_iff_evaluationPoint_mem (a : Fin 3) (q : ℂ × ℂ) (t : ℂ) :
    (ProjectivePlane.param a q,t) ∈ baseAway ↔
      evaluationPoint ![q.1,q.2,t] ∈ zariskiComplement a := by
  rw [baseAway_affine_iff]
  simp only [zariskiComplement,Opens.mem_iSup,evaluationPoint_mem_zariskiChart]
  constructor
  · intro h
    classical
    have hh : ∀ r, ∃ e : Fin 2, eval ![q.1,q.2,t] (affinePair a r e) ≠ 0 := by
      intro r
      exact (h r).elim (fun h0 => ⟨0,h0⟩) (fun h1 => ⟨1,h1⟩)
    choose e he using hh
    exact ⟨e,he⟩
  · rintro ⟨e,he⟩ r
    have hr := he r
    generalize e r = er at hr
    fin_cases er
    · exact Or.inl hr
    · exact Or.inr hr

abbrev ChartRing (a : Fin 3) (e : Fin 4 → Fin 2) := Localization.Away (chartDenominator a e)

theorem denominator_isUnit (a : Fin 3) (e : Fin 4 → Fin 2) (r : Fin 4) :
    IsUnit (algebraMap AffinePolynomial (ChartRing a e) (affinePair a r (e r))) := by
  apply IsLocalization.Away.isUnit_of_dvd (chartDenominator a e)
  exact Finset.dvd_prod_of_mem _ (Finset.mem_univ r)

/-- A regular affine-coordinate function in the ring of the actual principal open. -/
def localizedDirectionCoordinate (a : Fin 3) (e : Fin 4 → Fin 2) (r : Fin 4) : ChartRing a e :=
  algebraMap AffinePolynomial (ChartRing a e) (affinePair a r (e r).rev) *
    ↑((denominator_isUnit a e r).unit⁻¹)

theorem localizedDirectionCoordinate_mul_denominator (a : Fin 3) (e : Fin 4 → Fin 2) (r : Fin 4) :
    localizedDirectionCoordinate a e r *
      algebraMap AffinePolynomial (ChartRing a e) (affinePair a r (e r)) =
        algebraMap AffinePolynomial (ChartRing a e) (affinePair a r (e r).rev) := by
  have hu : (↑((denominator_isUnit a e r).unit⁻¹) : ChartRing a e) *
      algebraMap AffinePolynomial (ChartRing a e) (affinePair a r (e r)) = 1 := by
    simpa only [IsUnit.unit_spec] using (Units.inv_mul (denominator_isUnit a e r).unit)
  rw [localizedDirectionCoordinate,mul_assoc,hu,mul_one]

/-- Evaluation extends to the principal localization exactly when its defining
polynomial does not vanish at the complex point. -/
def evaluateChartRing (a : Fin 3) (e : Fin 4 → Fin 2) (q : Fin 3 → ℂ)
    (hq : evaluationPoint q ∈ zariskiChart a e) : ChartRing a e →+* ℂ :=
  IsLocalization.Away.lift (chartDenominator a e)
    (isUnit_iff_ne_zero.mpr ((evaluationPoint_mem_basicOpen q _).mp hq))

@[simp] theorem evaluateChartRing_algebraMap (a : Fin 3) (e : Fin 4 → Fin 2) (q : Fin 3 → ℂ)
    (hq : evaluationPoint q ∈ zariskiChart a e) (f : AffinePolynomial) :
    evaluateChartRing a e q hq (algebraMap AffinePolynomial (ChartRing a e) f) = eval q f :=
  IsLocalization.Away.lift_eq _ _ _

theorem evaluateChartRing_coordinate (a : Fin 3) (e : Fin 4 → Fin 2) (r : Fin 4)
    (q : Fin 3 → ℂ) (hq : evaluationPoint q ∈ zariskiChart a e) :
    evaluateChartRing a e q hq (localizedDirectionCoordinate a e r) =
      eval q (affinePair a r (e r).rev) / eval q (affinePair a r (e r)) := by
  apply (eq_div_iff ((evaluationPoint_mem_zariskiChart a e q).mp hq r)).mpr
  have h := congrArg (evaluateChartRing a e q hq)
    (localizedDirectionCoordinate_mul_denominator a e r)
  simpa only [map_mul,evaluateChartRing_algebraMap] using h

/-- These genuine regular localized functions equal the coordinates of the
already constructed analytic inverse. -/
theorem localized_coordinate_eq_lift (a : Fin 3) (e : Fin 4 → Fin 2) (r : Fin 4)
    (q : ℂ × ℂ) (t : ℂ)
    (hq : evaluationPoint ![q.1,q.2,t] ∈ zariskiChart a e) :
    evaluateChartRing a e ![q.1,q.2,t] hq (localizedDirectionCoordinate a e r) =
      ProjectiveLine.coordinates (e r) (directions (lift (ProjectivePlane.param a q,t)) r) := by
  rw [evaluateChartRing_coordinate]
  symm
  apply lift_direction_coordinate
  · apply (baseAway_iff_evaluationPoint_mem a q t).mpr
    exact Opens.mem_iSup.mpr ⟨e,hq⟩
  · exact (evaluationPoint_mem_zariskiChart a e _).mp hq r

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.BlowdownComplement
